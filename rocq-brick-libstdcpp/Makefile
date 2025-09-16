.PHONY: proof/dune.inc

proof: proof/dune.inc
	dune b

proof/dune.inc: proof/dune-gen.sh proof/cpp2v-dune-gen.sh
	(cd proof; ./dune-gen.sh)

