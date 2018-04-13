iimc-truss-2018-09-28

This is a modified version of iimc with proof-of-concept versions of Quip and
Truss integrated.

For build instructions, see README-iimc.

A brief summary of the bigger changes is as follows:
- The quip tactic 
- The truss tactic
- A different competition tactic using 4 threads (ic3, quip, truss, bmc)
- SAT backends are added for Glucose and Picosat

Quip
=================================

To run Quip with recommended options:

> $ iimc -t quip *aig*

Many additional options are available. 

Truss
=================================

To run Truss with recommended options:

> $ iimc -t truss *aig*


Various other options are available in Quip and Truss. For instance, it's
possible to run Truss with the re-enqueue operations enabled. It's also
possible to change the effort limit, to change the minimum level at which
support graphs apply, and many other possibilities. There are too many to 
fully describe here. See --help for more details.

IC3
=================================

To run IC3 with the feature set that most closely matches Quip and Truss:

> $ iimc -t ic3 --ic3\_xeqprop --ic3\_ctg 0 --ic3\_xbddInit 

Future Development
=================================

Currently the new tactics do not support SAT-based initiation checks and aiger
constraint, and therefore do not work with some circuit preprocesing passes.

A lot of tuning is possible, particularly with Truss. It may exhibit 
substantially different trade-offs than IC3 and therefore perform best
under much different parameters.

