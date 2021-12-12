#!/bin/zsh
export AWS_REGION=us-east-2
export AWS_ACCESS_KEY_ID=$(cat ~/.aws/credentials | grep access_key_id | awk '{print $3}')
export AWS_SECRET_ACCESS_KEY=$(cat ~/.aws/credentials | grep secret_access_key | awk '{print $3}')
export AWS_SESSION_TOKEN=$(cat ~/.aws/credentials | grep session_token | awk '{print $3}')
nim c --run -d:release -d:ssl main.nim $@
