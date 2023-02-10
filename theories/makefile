all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq Makefile.coq.conf

gitclean: 
	git clean -Xfd

findclean: 
	find \( -name "*.aux" -o -name "*.vo*" -o -name "*.glob" \) -exec rm -f {} \;

mrproper: clean gitclean findclean

# The *_private targets are only usable in the git repo, not in the artifact itself
diffs_private:
	git diff murec_artifact..murec_artifact_unit --output=unit.diff *.v
	git diff murec_artifact..murec_artifact_hide --output=hide.diff *.v

artifact_private: diffs_private
	tar zcvf artifact.tar.gz README.txt _CoqProject *.v *.diff makefile switch.pl 

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force

