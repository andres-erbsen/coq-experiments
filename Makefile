NAMESPACE=experiments

.PHONY: coq clean
coq: Makefile.coq
	$(MAKE) -f Makefile.coq
Makefile.coq: Makefile _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o $@
clean:
	$(MAKE) -f Makefile.coq clean || true
	rm -f Makefile.coq || true
	rm -f Makefile.coq.conf || true

update-_CoqProject::
	( printf -- "-Q $(NAMESPACE) $(NAMESPACE)\n-arg -noinit\n"; find "$(NAMESPACE)" -type f -name '*.v' ) | LC_COLLATE=C sort > _CoqProject
