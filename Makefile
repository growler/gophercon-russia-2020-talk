TOP := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))

CWD := $(shell pwd)

CACHE_PATH = $(TOP)/.latex-cache
MEDIA_PATH = $(TOP)/media

ifdef NOTIFY
  ifeq ($(shell which terminal-notifier),)
    notify       = osascript -e 'display notification "Slide $(@F) processed" with title "Slides processor"';
    notify_error = osascript -e 'display notification "Error processing slide $(@F)" with title "Slides processor"';
  else
    notify       = terminal-notifier -message "Slide $(@F) processed" -title "Slides processor" -open "file://$(TOP)/$(@F)";
    notify_error = terminal-notifier -message "Error processing slide $(@F)";
  endif
endif

THEME_SOURCES = $(MEDIA_PATH)/beamerthemegophercon.sty $(MEDIA_PATH)/itoolabs-graphics.sty $(MEDIA_PATH)/itoolabs-graphics.lua

talk: talk.pdf

all: svg talk clean

%.pdf: %.tex $(THEME_SOURCES)
	@printf "Producing %s (see %s)..." "$(@F)" "$(call relpath,$(CACHE_PATH)/$(notdir $(<:.tex=))-build.log)" ; \
	 printf "pass 1..." ; \
	 export TEXINPUTS=$(TOP)/:$(CACHE_PATH)/:$(MEDIA_PATH)//:$${TEXINPUTS} ; \
	 lualatex --shell-escape --halt-on-error --output-format=pdf \
		  --output-directory=$(CACHE_PATH) "\\def\\outputdir{$(CACHE_PATH)}\\input{$<}" \
		  > $(CACHE_PATH)/$(notdir $(<:.tex=))-build.log </dev/null ; \
	 if [[ $$? != 0 ]]; then \
	 	printf "error!\n"; tail -n 25 $(CACHE_PATH)/$(notdir $(<:.tex=))-build.log ; \
		$(call notify_error) exit -1; \
	 fi ;\
	 printf "pass 2..." ;\
	 lualatex --shell-escape --halt-on-error --output-format=pdf \
		  --output-directory=$(CACHE_PATH) "\\def\\outputdir{$(CACHE_PATH)}\\input{$<}" \
		  > $(CACHE_PATH)/$(notdir $(<:.tex=))-build.log </dev/null ; \
	 if [[ $$? != 0 ]]; then \
		printf "error!\n"; tail -n 25 $(CACHE_PATH)/$(notdir $(<:.tex=))-build.log ; \
		$(call notify_error) exit - 1; \
	 else \
		$(call notify) printf "done\n" ; \
		cp $(CACHE_PATH)/$(@F) $@ ; \
		if [ -n "$(OPENRESULT)" ]; then open -g -a Preview $@ ; fi ;\
	 fi

define FILTER_LEGEND
BEGIN {graph_t sg;}
BEG_G {sg = isSubg(root, "cluster_legend"); }
N[$$ != NULL] {if (sg != NULL && isSubnode(sg,$$) !=0 ) delete(root,$$); }
END_G { if (sg != NULL) delete(root, sg); }
endef

%.pdot: %.dot
	gvpr -c '$(strip $(FILTER_LEGEND))' "$<" > "$@"

%.svg: %.dot
	@gvpr -c "$(strip $(FILTER_LEGEND))" "$<" |\
	 dot -Tsvg -o "$@"

%.png: %.dot
	@gvpr -c "$(strip $(FILTER_LEGEND))" "$<" |\
	 dot -Tpng -Gdpi=300 -o "$@"

%.tikz: %.dot
	gvpr -c "$(strip $(FILTER_LEGEND))" "$<" |\
	 dot -Txdot | dot2tex --figonly > "$@" 
#	 sed '/\{\$/{s/\\n/ \\\\ /g;s/\\"//g;s/\/\\\\/\\land /g}' 

%.dot: %.tla
	@tlc -dump dot "$@" "$<" && \
	 rm -f "$(basename $<)_liveness.dot"

pictures: svg png tikz

define PICTURES
	00_Demo
	01_Demo
	03_Demo
	05_Channel
	25_ChannelBug
endef

svg: $(foreach p,$(PICTURES),$p.svg)
png: $(foreach p,$(PICTURES),$p.png)
tikz: $(foreach p,$(PICTURES),$p.tikz)

watch: $(filter-out watch,$(MAKECMDGOALS))
	@echo "Watching for changes. Keep writing!"
	@fswatch -r $(THEME_SOURCES) $(wildcard $(TOP)/*.tex) | (while read f; do \
		if [ -n "$(OPENRESULT)" ]; then do_open="OPENRESULT=1"; fi; \
		$(MAKE) NOTIFY=1 $$do_open $^; \
	 done )

clean:
	@find . -depth 1 -name \*.old -exec rm '{}' \;

help:
	cd $(TOP) && make -p .none | sed -n '/Not a target/{N;d;};s/^\([[:alnum:]][-[:alnum:]]*\):$$/\1/p' | sort

test-channel-bug:
	go test -v -run TestTimingOutProcess

test-buffer-1:
	go test -v -run TestBuffer1

test-buffer-2:
	go test -v -run TestBuffer2

$(CACHE_PATH):
	@mkdir -p $(CACHE_PATH)

.none:
	@echo

.PRECIOUS: %.dot

.PHONY: tikz pictures
.PHONY: $(CACHE_PATH) watch talk clean all .none svg test-channel-bug test-buffer-1 test-buffer-2
