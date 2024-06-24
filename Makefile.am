SUBDIRS = src

.PHONY: test ftest
test:
	$(MAKE) -C src
	cd $(top_srcdir)/scripts && ./driver.sh --debug

ftest:
	$(MAKE) -C src
	cd $(top_srcdir)/scripts && ./driver.sh --fast --debug

ctest:
	$(MAKE) -C src
	cd $(top_srcdir)/scripts && ./driver.sh --fast

rtest:
	$(MAKE) -C src
	cd $(top_srcdir)/scripts && ./randomize-driver.sh
