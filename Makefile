AGDA = agda
AGDA_OPTS = -i .


all: check pack

clean:
	find . -name "*.agda[ie]" -exec rm \{\} \; ; \
	find . -name "*~" -exec rm \{\} \;

check: force
	$(AGDA) $(AGDA_OPTS) Readme.agda

html: force
	$(AGDA) $(AGDA_OPTS) --html Readme.agda 

pack: html
	cd ..; \
	tar -cvzf model.tar.gz --exclude='*.agda[ie]' --exclude='*~'  model


force: 
	true
