AM_CXXFLAGS = -ffloat-store

AM_CPPFLAGS = -I$(srcdir)/..  -I$(srcdir)/simp -I$(srcdir)/mcore -I$(srcdir)/mtl -I$(srcdir)/utils -D __STDC_LIMIT_MACROS -D __STDC_FORMAT_MACROS


noinst_LIBRARIES = libglucose.a

libglucose_a_SOURCES = \
  simp/SimpSolver.cc \
  simp/SimpSolver.h \
  mcore/Solver.cc \
  mcore/Solver.h \
  mcore/SolverTypes.h \
  mcore/SolverStats.h \
  mcore/Constants.h \
  mcore/Dimacs.h \
  mcore/BoundedQueue.h \
  mtl/Alg.h \
  mtl/Alloc.h \
  mtl/Clone.h \
  mtl/Heap.h \
  mtl/IntTypes.h \
  mtl/Map.h \
  mtl/Queue.h \
  mtl/Sort.h \
  mtl/Vec.h \
  mtl/VecThreads.h \
  mtl/XAlloc.h \
  utils/Options.h \
  utils/Options.cc \
  utils/ParseUtils.h \
  utils/System.h \
  utils/System.cc

EXTRA_DIST = simp/Main.cc
