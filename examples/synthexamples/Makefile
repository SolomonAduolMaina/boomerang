GENERATE_DATA := python generate-data.py

generate-data:
	$(GENERATE_DATA) ../../boomerang.native optician_specs/
	mv generated_data/data.csv generated_data/optician_comparison_data.csv
	$(GENERATE_DATA) ../../boomerang.native new_specs/
	mv generated_data/data.csv generated_data/new_comparison_data.csv
	$(GENERATE_DATA) ../../boomerang.native new_optician_specs/
	mv generated_data/data.csv generated_data/new_optician_comparison_data.csv

generate-io-specs: cmdline.native
	$(GENERATE_IO_SPECS) ./cmdline.native example-inputs/ 10100

generate-extraction-specs: cmdline.native
	$(GENERATE_EXTRACTION_SPECS) ./cmdline.native example-inputs/ 10100

generate-boomerang-specs: cmdline.native
	$(GENERATE_BOOMERANG_SPECS) ./cmdline.native example-inputs/

profile: cmdline.p.native
	instruments -t "/Applications/Xcode.app/Contents/Applications/Instruments.app/Contents/Resources/templates/Time Profiler.tracetemplate" cmdline.p.native

unittest: unittests.native
	./unittests.native

functionaltest: cmdline.native
	$(CHECK_WITH_BOOMERANG) ./cmdline.native tests/

test: unittest functionaltest
