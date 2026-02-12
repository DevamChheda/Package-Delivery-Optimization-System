#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/ipc.h>
#include <sys/shm.h>
#include <sys/msg.h>
#include <pthread.h>
#include <stdint.h>
#include <time.h>

#define MAX_TRUCKS 250
#define TRUCK_MAX_CAP 20
#define MAX_NEW_reqS 50
#define MAX_TOTAL_PACKAGES 5000
#define MAX_AUTH_LENGTH 21
#define MAX_GRID 500

typedef struct {
    int truckId;
    int length;
    char result[MAX_AUTH_LENGTH];
    volatile uint8_t active;
    volatile uint8_t solved;
} AuthJob;

typedef struct {
    long mtype;
    int truckNumber;
    char authStringGuess[MAX_AUTH_LENGTH];
} Solverreq;

typedef struct {
    int packageId;
    int pickup_x;
    int pickup_y;
    int dropoff_x;
    int dropoff_y;
    int arrival_turn;
    int expiry_turn;
} packageReq;

typedef struct {
    long mtype;
} TurnReadyreq;

typedef struct {
    packageReq req;
    uint8_t state;
    uint8_t valid;
    int16_t assignedTruck;
    int16_t holder;
} PkgRecord;

typedef struct {
    long mtype;
    int guessIsCorrect;
} SolverResponse;

typedef struct {
    char authStrings[MAX_TRUCKS][MAX_AUTH_LENGTH];
    char truckMovementInstructions[MAX_TRUCKS];
    int pickUpCommands[MAX_TRUCKS];
    int dropOffCommands[MAX_TRUCKS];
    int truckPositions[MAX_TRUCKS][2];
    int truckPackageCount[MAX_TRUCKS];
    int truckTurnsInToll[MAX_TRUCKS];
    packageReq newpackageReqs[MAX_NEW_reqS];
    int packageLocations[MAX_TOTAL_PACKAGES][2];
} MainSharedMemory;

typedef struct {
    int N;
    int D;
    int S;
    int T;
    int B;
    key_t shmKey;
    key_t mainMqKey;
    key_t solverMqKeys[MAX_TRUCKS];
} InputData;

typedef struct {
    long mtype;
    int turnNumber;
    int newpackageReqCount;
    int errorOccurred;
    int finished;
} TurnChangeResponse;

static int toll_cost[MAX_GRID][MAX_GRID];
static pthread_t threads[MAX_TRUCKS];
static uint8_t toll_seen[MAX_GRID][MAX_GRID];
static int active_list[MAX_TOTAL_PACKAGES];
static volatile uint8_t stop_threads = 0;
static int16_t target[MAX_TRUCKS];
static pthread_mutex_t lock = PTHREAD_MUTEX_INITIALIZER;
static int master_mq = -1;
static uint8_t mode[MAX_TRUCKS];
static InputData CFG;
static pthread_cond_t cond_newjob = PTHREAD_COND_INITIALIZER;
static int active_count = 0;
static MainSharedMemory *shared_mem = NULL;
static int solver_q[MAX_TRUCKS];
static AuthJob auth_tasks[MAX_TRUCKS];
static uint8_t pkg_count[MAX_TRUCKS];
static pthread_cond_t cond_jobsdone = PTHREAD_COND_INITIALIZER;
static PkgRecord package_db[MAX_TOTAL_PACKAGES];
static int16_t pkg_slots[MAX_TRUCKS][TRUCK_MAX_CAP];

static inline int abs_diff(int firstVal, int secondVal){ return firstVal > secondVal ? firstVal - secondVal : secondVal - firstVal; }
static inline int distMan(int xOne, int yOne, int xTwo, int yTwo){ return abs_diff(xOne, xTwo) + abs_diff(yOne, yTwo); }

static int crack_auth_opt(int solverId, int truckId, int authLen, char *output){
    if(authLen <= 0 || authLen > 20 || solverId >= CFG.S) return 0;
    int messageQueue = solver_q[solverId];
    Solverreq solverReq = {2, truckId, ""};
    msgsnd(messageQueue, &solverReq, sizeof(solverReq) - sizeof(long), 0);
    static const char directionChars[4] = {'u','d','l','r'};
    char guessBuffer[21];
    uint32_t indexArray[21] = {0};
    for(long long attemptNum = 0;; attemptNum++){
        if(stop_threads) return 0;
        for(int charPos = 0; charPos < authLen; charPos++){
            guessBuffer[charPos] = directionChars[indexArray[charPos]];
        }
        guessBuffer[authLen] = 0;
        Solverreq guessReq = {3, 0, ""};
        memcpy(guessReq.authStringGuess, guessBuffer, authLen + 1);
        if(msgsnd(messageQueue, &guessReq, sizeof(guessReq) - sizeof(long), 0) < 0) return 0;
        SolverResponse response;
        if(msgrcv(messageQueue, &response, sizeof(response) - sizeof(long), 4, 0) < 0){
            return 0;
        }
        if(response.guessIsCorrect){
            memcpy(output, guessBuffer, authLen + 1);
            return 1;
        }
        int carryOver = 1;
        for(int digitPos = authLen - 1; digitPos >= 0 && carryOver; digitPos--){
            if(++indexArray[digitPos] < 4) carryOver = 0;
            else indexArray[digitPos] = 0;
        }
        if(carryOver) break;
    }
    return 0;
}

static void* worker_thread(void *arg){
    int solverId = *(int*)arg;
    free(arg);
    while(!stop_threads){
        int myJobIndex = -1;
        int minAuthLen = 999;
        pthread_mutex_lock(&lock);
        while(myJobIndex == -1 && !stop_threads){
            minAuthLen = 999;
            myJobIndex = -1;
            int truckIdx = 0;
            while(truckIdx < CFG.D){
                if(auth_tasks[truckIdx].active == 1 && !auth_tasks[truckIdx].solved && auth_tasks[truckIdx].length < minAuthLen){
                    minAuthLen = auth_tasks[truckIdx].length;
                    myJobIndex = truckIdx;
                }
                truckIdx++;
            }
            if(myJobIndex != -1){
                auth_tasks[myJobIndex].active = 2;
            } else if(!stop_threads){
                pthread_cond_wait(&cond_newjob, &lock);
            }
        }
        pthread_mutex_unlock(&lock);
        if(stop_threads || myJobIndex == -1) break;
        int wasSolved = crack_auth_opt(solverId, auth_tasks[myJobIndex].truckId, auth_tasks[myJobIndex].length, auth_tasks[myJobIndex].result);
        pthread_mutex_lock(&lock);
        if(wasSolved) auth_tasks[myJobIndex].solved = 1;
        auth_tasks[myJobIndex].active = 0;
        pthread_cond_signal(&cond_jobsdone);
        pthread_mutex_unlock(&lock);
    }
    return NULL;
}

static void init_ipc(void){
    int shmId = shmget(CFG.shmKey, sizeof(MainSharedMemory), 0666);
    if(shmId < 0) exit(1);
    shared_mem = (MainSharedMemory*)shmat(shmId, NULL, 0);
    if(shared_mem == (void*)-1) exit(1);
    master_mq = msgget(CFG.mainMqKey, 0666);
    if(master_mq < 0) exit(1);
    int solverIdx = 0;
    while(solverIdx < CFG.S){
        solver_q[solverIdx] = msgget(CFG.solverMqKeys[solverIdx], 0666);
        if(solver_q[solverIdx] < 0) exit(1);
        solverIdx++;
    }
    memset(package_db, 0, sizeof(package_db));
    memset(mode, 0, sizeof(mode));
    for(solverIdx = 0; solverIdx < MAX_TRUCKS; solverIdx++) target[solverIdx] = -1;
    for(solverIdx = 0; solverIdx < MAX_TRUCKS; solverIdx++) { int slotIdx = 0; while(slotIdx < TRUCK_MAX_CAP){ pkg_slots[solverIdx][slotIdx] = -1; slotIdx++; } }
    memset(pkg_count, 0, sizeof(pkg_count));
    memset(auth_tasks, 0, sizeof(auth_tasks));
    memset(toll_cost, 0, sizeof(toll_cost));
    memset(toll_seen, 0, sizeof(toll_seen));
    solverIdx = 0;
    while(solverIdx < CFG.S){
        int *threadArg = malloc(sizeof(int));
        *threadArg = solverIdx;
        pthread_create(&threads[solverIdx], NULL, worker_thread, threadArg);
        solverIdx++;
    }
}

static void load_input(void){
    FILE *inputFile = fopen("input.txt","r");
    if(!inputFile) exit(1);
    fscanf(inputFile, "%d%d%d%d%d", &CFG.N, &CFG.D, &CFG.S, &CFG.T, &CFG.B);
    unsigned long long keyValue;
    fscanf(inputFile, "%llu", &keyValue); CFG.shmKey = (key_t)keyValue;
    fscanf(inputFile, "%llu", &keyValue); CFG.mainMqKey = (key_t)keyValue;
    int solverIdx = 0;
    while(solverIdx < CFG.S){ fscanf(inputFile, "%llu", &keyValue); CFG.solverMqKeys[solverIdx] = (key_t)keyValue; solverIdx++; }
    fclose(inputFile);
}

static void refresh_tolls(void){
    int truckIdx = 0;
    while(truckIdx < CFG.D){
        if(shared_mem->truckTurnsInToll[truckIdx] > 0){
            int xCoord = shared_mem->truckPositions[truckIdx][0];
            int yCoord = shared_mem->truckPositions[truckIdx][1];
            if(xCoord >= 0 && xCoord < CFG.N && yCoord >= 0 && yCoord < CFG.N){
                if(shared_mem->truckTurnsInToll[truckIdx] > toll_cost[xCoord][yCoord]){
                    toll_cost[xCoord][yCoord] = shared_mem->truckTurnsInToll[truckIdx];
                    toll_seen[xCoord][yCoord] = 1;
                }
            }
        }
        truckIdx++;
    }
}

static inline char choose_move(int gridSize, int currentX, int currentY, int targetX, int targetY){
    char possibleMoves[4];
    int moveCosts[4];
    int moveCount = 0;
    const int toll_penalty_multiplier = 3;
    if(currentX < targetX && currentX + 1 < gridSize){
        possibleMoves[moveCount] = 'r';
        moveCosts[moveCount] = 1 + (toll_seen[currentX + 1][currentY] ? toll_cost[currentX + 1][currentY] * toll_penalty_multiplier : 0);
        moveCount++;
    }
    if(currentX > targetX && currentX > 0){
        possibleMoves[moveCount] = 'l';
        moveCosts[moveCount] = 1 + (toll_seen[currentX - 1][currentY] ? toll_cost[currentX - 1][currentY] * toll_penalty_multiplier : 0);
        moveCount++;
    }
    if(currentY < targetY && currentY + 1 < gridSize){
        possibleMoves[moveCount] = 'd';
        moveCosts[moveCount] = 1 + (toll_seen[currentX][currentY + 1] ? toll_cost[currentX][currentY + 1] * toll_penalty_multiplier : 0);
        moveCount++;
    }
    if(currentY > targetY && currentY > 0){
        possibleMoves[moveCount] = 'u';
        moveCosts[moveCount] = 1 + (toll_seen[currentX][currentY - 1] ? toll_cost[currentX][currentY - 1] * toll_penalty_multiplier : 0);
        moveCount++;
    }
    if(moveCount == 0) return 's';
    int bestMoveIdx = 0;
    int moveIdx = 1;
    while(moveIdx < moveCount){
        if(moveCosts[moveIdx] < moveCosts[bestMoveIdx]) bestMoveIdx = moveIdx;
        moveIdx++;
    }
    return possibleMoves[bestMoveIdx];
}

static int calc_priority(packageReq *req, int truckX, int truckY, int currentTurn){
    int pickupDistance = distMan(truckX, truckY, req->pickup_x, req->pickup_y);
    int deliveryDistance = distMan(req->pickup_x, req->pickup_y, req->dropoff_x, req->dropoff_y);
    int totalDistance = pickupDistance + deliveryDistance;
    int slack = req->expiry_turn - currentTurn - totalDistance;
    if(slack < -10) return 2000000 + pickupDistance;
    if(slack < -5) return 1000000 + (100 - slack) * 1000 + pickupDistance;
    if(slack < 0) return 500000 + (20 - slack) * 5000 + pickupDistance;
    if(slack < 3) return 100000 + (10 - slack) * 2000 + pickupDistance;
    if(slack < 8) return 50000 + (15 - slack) * 500 + pickupDistance;
    if(slack < 15) return 10000 + (20 - slack) * 100 + pickupDistance;
    return pickupDistance * 50 + deliveryDistance * 20 + slack;
}

static int pick_best_pkg(int truckX, int truckY, int currentTurn, int truckId, int currentLoad){
    int bestPackageId = -1;
    int minPriority = 2000000000;
    int loadPenalty = currentLoad * 500;
    int listIdx = 0;
    while(listIdx < active_count){
        int packageId = active_list[listIdx];
        if(!package_db[packageId].valid || package_db[packageId].state != 0){ listIdx++; continue; }
        int packagePrior = calc_priority(&package_db[packageId].req, truckX, truckY, currentTurn) + loadPenalty;
        if(packagePrior < minPriority){
            minPriority = packagePrior;
            bestPackageId = packageId;
        }
        listIdx++;
    }
    return bestPackageId;
}

static int pick_next_delivery(int truckId, int truckX, int truckY, int currentTurn){
    int bestPackageId = -1;
    int minPriority = 2000000000;
    int slotIdx = 0;
    while(slotIdx < TRUCK_MAX_CAP){
        int packageId = pkg_slots[truckId][slotIdx];
        if(packageId < 0 || !package_db[packageId].valid){ slotIdx++; continue; }
        packageReq *req = &package_db[packageId].req;
        int deliveryDist = distMan(truckX, truckY, req->dropoff_x, req->dropoff_y);
        int slack = req->expiry_turn - currentTurn - deliveryDist;
        int packagePrior;
        if(slack < -10) packagePrior = 2000000 + deliveryDist;
        else if(slack < -5) packagePrior = 1000000 + (100 - slack) * 1000 + deliveryDist;
        else if(slack < 0) packagePrior = 500000 + (20 - slack) * 5000 + deliveryDist;
        else if(slack < 3) packagePrior = 100000 + (10 - slack) * 2000 + deliveryDist;
        else if(slack < 8) packagePrior = 50000 + (15 - slack) * 500 + deliveryDist;
        else if(slack < 15) packagePrior = 10000 + (20 - slack) * 100 + deliveryDist;
        else packagePrior = deliveryDist * 50 + slack;
        if(packagePrior < minPriority){
            minPriority = packagePrior;
            bestPackageId = packageId;
        }
        slotIdx++;
    }
    return bestPackageId;
}

static inline void put_package(int truckId, int packageId){
    int slotIdx = 0;
    while(slotIdx < TRUCK_MAX_CAP){
        if(pkg_slots[truckId][slotIdx] == -1){
            pkg_slots[truckId][slotIdx] = packageId;
            pkg_count[truckId]++;
            package_db[packageId].holder = truckId;
            return;
        }
        slotIdx++;
    }
}

static inline void take_package(int truckId, int packageId){
    int slotIdx = 0;
    while(slotIdx < TRUCK_MAX_CAP){
        if(pkg_slots[truckId][slotIdx] == packageId){
            pkg_slots[truckId][slotIdx] = -1;
            pkg_count[truckId]--;
            package_db[packageId].holder = -1;
            return;
        }
        slotIdx++;
    }
}

static void pull_in_packages(int packageCount){
    int reqIdx = 0;
    while(reqIdx < packageCount){
        packageReq req = shared_mem->newpackageReqs[reqIdx];
        if(req.packageId >= 0 && req.packageId < MAX_TOTAL_PACKAGES){
            package_db[req.packageId].valid = 1;
            package_db[req.packageId].req = req;
            package_db[req.packageId].holder = -1;
            if(package_db[req.packageId].state != 2){
                package_db[req.packageId].state = 0;
                package_db[req.packageId].assignedTruck = -1;
                if(active_count < MAX_TOTAL_PACKAGES) active_list[active_count++] = req.packageId;
            }
        }
        reqIdx++;
    }
}

static void cleanup_active_packages(void){
    int newActiveCount = 0;
    int listIdx = 0;
    while(listIdx < active_count){
        int packageId = active_list[listIdx];
        if(package_db[packageId].valid && package_db[packageId].state != 3){
            active_list[newActiveCount++] = packageId;
        }
        listIdx++;
    }
    active_count = newActiveCount;
}

static void handle_turn(int currentTurn){
    int truckIdx = 0;
    while(truckIdx < CFG.D){
        shared_mem->truckMovementInstructions[truckIdx] = 's';
        shared_mem->pickUpCommands[truckIdx] = -1;
        shared_mem->dropOffCommands[truckIdx] = -1;
        shared_mem->authStrings[truckIdx][0] = 0;
        truckIdx++;
    }
    cleanup_active_packages();
    int activeTruckIdx = 0;
    while(activeTruckIdx < CFG.D){
        if(shared_mem->truckTurnsInToll[activeTruckIdx] > 0){
            activeTruckIdx++;
            continue;
        }
        int currentX = shared_mem->truckPositions[activeTruckIdx][0];
        int currentY = shared_mem->truckPositions[activeTruckIdx][1];
        if(currentX < 0 || currentX >= CFG.N || currentY < 0 || currentY >= CFG.N){
            activeTruckIdx++;
            continue;
        }
        if(mode[activeTruckIdx] == 0){
            if(pkg_count[activeTruckIdx] > 0){
                int deliveryPackageId = pick_next_delivery(activeTruckIdx, currentX, currentY, currentTurn);
                if(deliveryPackageId != -1){ mode[activeTruckIdx] = 2; target[activeTruckIdx] = deliveryPackageId; }
            }
            if(mode[activeTruckIdx] == 0 && pkg_count[activeTruckIdx] < (TRUCK_MAX_CAP / 2)){
                int pickupPackageId = pick_best_pkg(currentX, currentY, currentTurn, activeTruckIdx, pkg_count[activeTruckIdx]);
                if(pickupPackageId != -1){
                    package_db[pickupPackageId].state = 1;
                    package_db[pickupPackageId].assignedTruck = activeTruckIdx;
                    mode[activeTruckIdx] = 1;
                    target[activeTruckIdx] = pickupPackageId;
                }
            }
        }
        if(mode[activeTruckIdx] == 1 && target[activeTruckIdx] != -1){
            packageReq *req = &package_db[target[activeTruckIdx]].req;
            if(currentX == req->pickup_x && currentY == req->pickup_y && pkg_count[activeTruckIdx] < TRUCK_MAX_CAP){
                shared_mem->pickUpCommands[activeTruckIdx] = req->packageId;
                package_db[req->packageId].state = 2;
                put_package(activeTruckIdx, req->packageId);
                int sameLocationPackage = -1;
                if(pkg_count[activeTruckIdx] < (TRUCK_MAX_CAP / 2)){
                    int searchIdx = 0;
                    while(searchIdx < active_count){
                        int candidateId = active_list[searchIdx];
                        if(!package_db[candidateId].valid || package_db[candidateId].state != 0){ searchIdx++; continue; }
                        packageReq *candidateReq = &package_db[candidateId].req;
                        if(candidateReq->pickup_x == currentX && candidateReq->pickup_y == currentY){
                            int candidateSlack = candidateReq->expiry_turn - currentTurn - distMan(currentX, currentY, candidateReq->dropoff_x, candidateReq->dropoff_y);
                            if(candidateSlack < 10){ sameLocationPackage = candidateId; break; }
                        }
                        searchIdx++;
                    }
                }
                if(sameLocationPackage != -1){
                    package_db[sameLocationPackage].state = 1;
                    package_db[sameLocationPackage].assignedTruck = activeTruckIdx;
                    mode[activeTruckIdx] = 1;
                    target[activeTruckIdx] = sameLocationPackage;
                } else {
                    int nextDelivery = pick_next_delivery(activeTruckIdx, currentX, currentY, currentTurn);
                    if(nextDelivery != -1){ mode[activeTruckIdx] = 2; target[activeTruckIdx] = nextDelivery; }
                    else { mode[activeTruckIdx] = 0; target[activeTruckIdx] = -1; }
                }
            } else {
                shared_mem->truckMovementInstructions[activeTruckIdx] = choose_move(CFG.N, currentX, currentY, req->pickup_x, req->pickup_y);
            }
        }
        if(mode[activeTruckIdx] == 2 && target[activeTruckIdx] != -1){
            packageReq *req = &package_db[target[activeTruckIdx]].req;
            if(currentX == req->dropoff_x && currentY == req->dropoff_y && package_db[req->packageId].holder == activeTruckIdx){
                shared_mem->dropOffCommands[activeTruckIdx] = req->packageId;
                package_db[req->packageId].state = 3;
                package_db[req->packageId].assignedTruck = -1;
                take_package(activeTruckIdx, req->packageId);
                int sameLocationPackage = -1;
                int slotIdx = 0;
                while(slotIdx < TRUCK_MAX_CAP){
                    int carriedPackageId = pkg_slots[activeTruckIdx][slotIdx];
                    if(carriedPackageId >= 0 && package_db[carriedPackageId].valid){
                        packageReq *carriedReq = &package_db[carriedPackageId].req;
                        if(carriedReq->dropoff_x == currentX && carriedReq->dropoff_y == currentY){ sameLocationPackage = carriedPackageId; break; }
                    }
                    slotIdx++;
                }
                if(sameLocationPackage != -1){
                    mode[activeTruckIdx] = 2;
                    target[activeTruckIdx] = sameLocationPackage;
                } else if(pkg_count[activeTruckIdx] > 0){
                    int nextDelivery = pick_next_delivery(activeTruckIdx, currentX, currentY, currentTurn);
                    if(nextDelivery != -1){ mode[activeTruckIdx] = 2; target[activeTruckIdx] = nextDelivery; }
                    else { mode[activeTruckIdx] = 0; target[activeTruckIdx] = -1; }
                } else {
                    mode[activeTruckIdx] = 0;
                    target[activeTruckIdx] = -1;
                }
            } else {
                shared_mem->truckMovementInstructions[activeTruckIdx] = choose_move(CFG.N, currentX, currentY, req->dropoff_x, req->dropoff_y);
            }
        }
        activeTruckIdx++;
    }
    pthread_mutex_lock(&lock);
    int jobsCreated = 0;
    int jobIdx = 0;
    while(jobIdx < CFG.D){
        if(shared_mem->truckMovementInstructions[jobIdx] != 's' && shared_mem->truckPackageCount[jobIdx] > 0){
            auth_tasks[jobIdx].active = 1;
            auth_tasks[jobIdx].truckId = jobIdx;
            auth_tasks[jobIdx].length = shared_mem->truckPackageCount[jobIdx];
            auth_tasks[jobIdx].solved = 0;
            jobsCreated++;
        } else {
            auth_tasks[jobIdx].active = 0;
            auth_tasks[jobIdx].solved = 0;
        }
        jobIdx++;
    }
    pthread_mutex_unlock(&lock);
    if(jobsCreated > 0) pthread_cond_broadcast(&cond_newjob);
    pthread_mutex_lock(&lock);
    while(1){
        int pendingJobs = 0;
        int checkIdx = 0;
        while(checkIdx < CFG.D){
            if(auth_tasks[checkIdx].active != 0) pendingJobs++;
            checkIdx++;
        }
        if(!pendingJobs) break;
        pthread_cond_wait(&cond_jobsdone, &lock);
    }
    pthread_mutex_unlock(&lock);
    int resultIdx = 0;
    while(resultIdx < CFG.D){
        if(auth_tasks[resultIdx].solved){
            memcpy(shared_mem->authStrings[resultIdx], auth_tasks[resultIdx].result, auth_tasks[resultIdx].length + 1);
        } else if(shared_mem->truckMovementInstructions[resultIdx] != 's' && shared_mem->truckPackageCount[resultIdx] > 0){
            shared_mem->truckMovementInstructions[resultIdx] = 's';
            shared_mem->authStrings[resultIdx][0] = 0;
        }
        resultIdx++;
    }
}

int main(void){
    load_input();
    init_ipc();
    TurnReadyreq ready = {1};
    TurnChangeResponse resp;
    while(1){
        if(msgrcv(master_mq, &resp, sizeof(resp) - sizeof(long), 2, 0) < 0) break;
        if(resp.errorOccurred || resp.finished) break;
        pull_in_packages(resp.newpackageReqCount);
        refresh_tolls();
        handle_turn(resp.turnNumber);
        if(msgsnd(master_mq, &ready, sizeof(ready) - sizeof(long), 0) < 0) break;
    }
    stop_threads = 1;
    pthread_mutex_lock(&lock);
    pthread_cond_broadcast(&cond_newjob);
    pthread_mutex_unlock(&lock);
    int threadIdx = 0;
    while(threadIdx < CFG.S){
        pthread_join(threads[threadIdx], NULL);
        threadIdx++;
    }
    pthread_mutex_destroy(&lock);
    pthread_cond_destroy(&cond_newjob);
    pthread_cond_destroy(&cond_jobsdone);
    shmdt(shared_mem);
    return 0;
}