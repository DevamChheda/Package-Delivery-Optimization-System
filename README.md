**High Performance Concurrent Delivery Scheduler**

Built a large scale delivery scheduling engine in POSIX compliant C that coordinates hundreds of trucks on a grid while minimizing delivery turns and expired packages. The system relies on shared memory and message queues for real time communication with helper and solver processes, where trucks carrying packages must obtain authorization strings before movement. 

Designed a pthread driven concurrent architecture with mutex guarded critical sections and lock free read paths to eliminate race conditions without introducing contention. Enforced strict lock ordering to ensure deadlock free execution even under heavy parallel workloads.

Developed a priority aware scheduler with fast spatial lookups to match trucks with nearby pickups, cutting delivery cycles significantly. Implemented thread safe pathfinding using atomic operations and cached toll states so trucks delayed by toll cells do not trigger redundant computations. 

Integrated a pooled worker pipeline for solver communication, using semaphores to keep authorization guessing non blocking and maintain steady throughput.

This project deepened my understanding of operating systems level concurrency and reinforced how thoughtful synchronization design directly translates into real performance gains.
