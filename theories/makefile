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

filelist_private: diffs_private
	echo README.md > filelist.txt
	echo theories/_CoqProject >> filelist.txt
	echo theories/makefile >> filelist.txt
	echo theories/switch.pl >> filelist.txt
	( cd .. && find \( -name "*.v" -o -name "*.diff" \) ) >> filelist.txt 

artifact_private: diffs_private
	tar -C .. -zcvf artifact.tar.gz -T filelist.txt

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

whitespaces: force
	find . -type f -name "*.v" -exec sed --in-place 's/[[:space:]]\+$$//' {} \+

wc: force
	coqwc `find -name "*.v"`

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force

