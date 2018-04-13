umc_UMC_sources = \
  src/umc/UMC.h \
  src/umc/UMC.cpp \
  src/umc/UMCEngine.h \
  src/umc/UMCEngine.cpp \
  src/umc/InductiveTrace.h \
  src/umc/InductiveTrace.cpp \
  src/umc/Consecution.h \
  src/umc/Consecution.cpp \
  src/umc/Generalization.h \
  src/umc/Generalization.cpp \
  src/umc/SupportGraph.h \
  src/umc/SupportGraph.cpp \
  src/umc/UMCIC3.h \
  src/umc/UMCIC3.cpp \
  src/umc/Quip.h \
  src/umc/Quip.cpp \
  src/umc/Truss.h \
  src/umc/Truss.cpp

iimc_SOURCES += $(umc_UMC_sources)

AM_CPPFLAGS += -I$(srcdir)/src/umc

check_PROGRAMS += test_UMC
TESTS += test_UMC

test_UMC_SOURCES = \
  src/umc/test_UMC.cpp \
  src/umc/UMC.h \
  src/umc/UMC.cpp \
  src/umc/UMCEngine.h \
  src/umc/UMCEngine.cpp \
  src/umc/InductiveTrace.h \
  src/umc/InductiveTrace.cpp \
  src/umc/Consecution.h \
  src/umc/Consecution.cpp \
  src/umc/Generalization.h \
  src/umc/Generalization.cpp \
  src/umc/SupportGraph.h \
  src/umc/SupportGraph.cpp \
  src/umc/UMCIC3.h \
  src/umc/UMCIC3.cpp \
  src/umc/Quip.h \
  src/umc/Quip.cpp \
  src/umc/Truss.h \
  src/umc/Truss.cpp \
  src/mc/COI.h \
  src/mc/COI.cpp \
  src/mc/ProofAttachment.h \
  src/mc/ProofAttachment.cpp \
  $(cnf_CNF_sources) \
  $(expressions_Expr_sources) \
  $(expressions_Attachment_sources) \
  $(model_Model_sources) \
  $(sat_SAT_sources) \
  $(util_Util_sources) \
  $(parser_Parser_sources) \
  $(copt_AIG_sources) 

