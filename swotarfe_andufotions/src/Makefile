%.vo: %.v
	coqc $<

SfLib.v:
	@mkdir -p .tmp
	@echo "Downloading..."
	wget --quiet -O ".tmp/sf.tar.gz" \
	  http://www.cis.upenn.edu/~bcpierce/sf/current/sf.tar.gz
	@tar -xf ".tmp/sf.tar.gz" -C ".tmp" sf/SfLib.v
	@mv ".tmp/sf/SfLib.v" .
	@rm -rf ".tmp"
	@echo "Validating checksum..."
	@if [ "5a9725cbfe5e0aecae00c8ca91354fce  SfLib.v" \
	  != "`md5sum SfLib.v`" ]; \
	  then rm SfLib.v; echo 'Checksum for SfLib.v does not match'; \
	  exit 1; fi

clean:
	rm *.vo *.glob

.PHONY: clean
