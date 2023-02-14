#! /bin/bash

# Copyright 2023 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#      http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.

# TODO(cascaval): add arguments to force downloading

mydir="$(realpath "$(dirname "$0")")"
mnist_dir="${mydir}/../data_sets/mnist/"

if [[ -e "$mnist_dir" ]]; then
  echo "$(realpath "${mnist_dir}") already exists. Skipping download!"
  exit 0
fi

mkdir -p "$mnist_dir"
cd ${mnist_dir}
echo "Downloading from https://data.deepai.org/mnist.zip"
wget "https://data.deepai.org/mnist.zip"
unzip mnist.zip
rm mnist.zip
gunzip *.gz

cd ${mydir}

exit 0
