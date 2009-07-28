#!/bin/bash

# TODO(rgrig): the version needs to be updated manually here, which sucks
java -ea -cp temp/:../dist/lib/clops-0.2.2.jar toyMain $*
