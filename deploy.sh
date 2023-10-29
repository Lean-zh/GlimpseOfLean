#!/usr/bin/env bash

# Exit on error
set -e

[ -z $LEAN_REMOTE_GLIMPSE ] && echo "LEAN_REMOTE_GLIMPSE not set" && exit 1

# Build
mdbook build

# Deploy
cd book
git init
git add .
git commit -m "Deploy $(date)"
git remote add origin $LEAN_REMOTE_GLIMPSE
git push --force origin +HEAD:gh-pages
