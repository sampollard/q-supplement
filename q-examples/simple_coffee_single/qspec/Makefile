SHELL := /bin/bash

qfile := simple_coffee/coffee_maker/coffee_maker

all: qspec smv

qspec:
	@eval "reset"
	@echo "The chosen one is: $(qfile).qspec"
	xmllint --xinclude $(qfile).qspec --output $(qfile).xmllint
	@echo "Generated $(qfile).xmllint"
	qwrang-xml < $(qfile).xmllint > $(qfile).qwrang
	@echo "Generated $(qfile).qwrang"
	qlang -f smv $(qfile).qwrang --prove -v -o $(qfile).smv
	@echo "Generated $(qfile).smv"

smv:
	NuSMV -ctt -df -dynamic $(qfile).smv > $(qfile).smvout

clean:
	rm $(qfile).xmllint $(qfile).qwrang $(qfile).smv $(qfile).smvout