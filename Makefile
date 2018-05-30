all: build

J=4

setup.ml: _oasis
	oasis setup

setup.data: setup.ml
	./configure

build: setup.data setup.ml
	ocaml setup.ml -build -j $(J)

install: setup.data setup.ml
	ocaml setup.ml -install

reinstall: setup.ml
	ocaml setup.ml -reinstall

uninstall: setup.ml
	ocaml setup.ml -uninstall

test: setup.ml build
	ocaml setup.ml -test $(TESTFLAGS)

clean:
	ocamlbuild -clean
	rm -f setup.data setup.log

distclean:
	ocaml setup.ml -distclean
	rm -f setup.data setup.log

doc:
	ocaml setup.ml -doc

generate-data: setup.data setup.ml
	ocaml setup.ml -build -j $(J)
	python generate-data.py ./boomerang.native examples/synthexamples/optician_specs/
	mv generated_data/data.csv generated_data/optician_comparison_data.csv
	python generate-data.py ./boomerang.native examples/synthexamples/new_specs/
	mv generated_data/data.csv generated_data/new_comparison_data.csv
	python generate-data.py ./boomerang.native examples/synthexamples/new_optician_specs/
	mv generated_data/data.csv generated_data/new_optician_comparison_data.csv
	python generate-size-data.py ./boomerang.native examples/synthexamples/new_specs/

generate-graphs:
	python transform-data.py generated_data/new_comparison_data.csv generated_data/optician_comparison_data.csv generated_data/oo_data.csv generated_data/new_optician_comparison_data.csv
	python transform-size-data.py generated_data/size_data.csv
