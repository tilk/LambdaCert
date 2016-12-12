#!/bin/bash

BASE_PATH=`dirname $0`/..

cd $BASE_PATH/tests

#NODE_PATH=/usr/lib/node_modules/ exec node $BASE_PATH/tests/jsparser_node.js $1
exec js24 jsparser_js.js esprima.js $1

