# Scheduling and allocation


Allocation: maps a Application to a HardwareSpec. An allocation consists of:
  - a mapping of app node and link handles to system spec node and link handles.

Scheduling: computes a schedule -- the sequencing of compute and communication
operations for an allocated application. A schedule consists of:
  - communication calendars for each link in the system;
  - communication calendars for each switch in the system (to be implemented);
  - a sequencing of function invocations for each compute node in the system.

NOTE: Currently, we only support a one-to-one mapping: that is, an
application assumes that the HardwareSpec has an isomorphic topology and
provides all resources required to execute the application. Therefore,
scheduling results in setting up the HardwareSpec with the data listed
above.
