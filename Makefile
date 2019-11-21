COQ_MAKEFILE=Makefile.coq

all: ${COQ_MAKEFILE}
	make -f ${COQ_MAKEFILE}

clean: ${COQ_MAKEFILE}
	make -f ${COQ_MAKEFILE} clean

${COQ_MAKEFILE}: _CoqProject
	coq_makefile -f _CoqProject -o $@
