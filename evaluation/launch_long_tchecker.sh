#!/bin/bash
cd "$(dirname "$0")"
LIMIT=${LIMIT:-3600} JOBS=${JOBS:-3} bash run_long_tchecker.sh > long_tchecker_master.log 2>&1
