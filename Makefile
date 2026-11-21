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


# The Rocq proofs, and Verilator simulators of simpleSpec (SimpleSim/) and nondetSpec (NondetSim/).
# The simulators reuse cheriot's testbench (SimTb.sv, TbCommon.sv) and run_all_tests.sh.
.PHONY: all coq rtl_bin simrtl simrtlexe force clean

.DEFAULT_GOAL = all

CURR_DIR = $(shell pwd)
SIMS = SimpleSim NondetSim
SIM_TARGETS = $(foreach d,$(SIMS),$(CURR_DIR)/$(d)/)

include ../Guru/Gallina.mk

Makefile.coq.all: force
	$(COQBIN)rocq makefile --no-rocq-package-warning -docroot SpecCheriot -f _CoqProject -o Makefile.coq.all

coq: Makefile.coq.all
	$(MAKE) -C ../cheriot coq
	$(MAKE) -f Makefile.coq.all

all: coq

rtl_bin: coq
	$(MAKE) -C ../Guru TARGETS="$(SIM_TARGETS)" $(foreach d,$(SIMS),$(CURR_DIR)/$(d)/Rtl)

simrtl: rtl_bin
	$(MAKE) -C ../Guru TARGETS="$(SIM_TARGETS)" simrtl

# SimTb.sv includes SimRtl.sv: a copy next to each SimRtl.sv picks up the right one.
# One rule per simulator, so that each command (in particular gallina_lib, which is
# "@true" without Gallina calls and "cd ... && ghc ..." with them) is a recipe line of its own.
# $(1) = simulator directory
define Simrtlexe_rule
$(1)/sim_obj_dir/VTb: simrtl
	cp ../cheriot/SimTb.sv $(1)/SimTb.sv
	$$(call gallina_lib,$(CURR_DIR)/$(1)/,$(1)/SimRtl.sv)
	verilator -Wno-CMPCONST --top Tb --binary -I../Guru/Verilog -I$(1) -I../cheriot --Mdir $(1)/sim_obj_dir $(1)/SimTb.sv $$(call gallina_args,$(CURR_DIR)/$(1)/,$(1)/SimRtl.sv)
endef

$(foreach d,$(SIMS),$(eval $(call Simrtlexe_rule,$(d))))

simrtlexe: $(foreach d,$(SIMS),$(d)/sim_obj_dir/VTb)

force:

clean:: Makefile.coq.all
	$(MAKE) -f Makefile.coq.all clean
	rm -f Makefile.coq.all Makefile.coq.all.conf .Makefile.coq.all.d
	rm -rf $(foreach d,$(SIMS),$(d)/sim_obj_dir $(d)/Compile.* $(d)/Rtl $(d)/*.hi $(d)/*.o $(d)/*.sv $(d)/libgallina.a)
