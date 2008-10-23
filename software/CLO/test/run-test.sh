#!/bin/bash

java -cp temp/:../dist/lib/CLO.jar ie.ucd.clops.dsl.parser.GeneratedParserTest Parser $*
