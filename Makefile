# Copyright 2026 Google LLC
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     https://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.


# Only the Rocq proofs; the Cheriot and Guru proofs are built first.
.PHONY: all coq force clean

.DEFAULT_GOAL = all

Makefile.coq.all: force
	$(COQBIN)rocq makefile --no-rocq-package-warning -docroot SpecCheriot -f _CoqProject -o Makefile.coq.all

coq: Makefile.coq.all
	$(MAKE) -C ../cheriot coq
	$(MAKE) -f Makefile.coq.all

all: coq

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
