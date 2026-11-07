COQC ?= rocq compile

CORE = MTL_to_TBA_Shared_Clock_Derived_Strict_Direct_Core
PROOF = EncodingCorrect_Shared_Clock_Derived_Strict_Direct_Proof
EXAMPLE = OverlappingResponse_Example
ZEROINIT = ZeroInit
SOUND = LTL_to_PBA_Sound
PACK = LTL_to_PBA_Pack
CONCRETE = LTL_to_PBA_Concrete
COMPLETE = LTL_to_PBA_Complete
FINAL = LTL_to_PBA_Final
ABSTRACT = ClockedLTL_Abstract
INSTANCE = ClockedLTL_Instance
NONMTL = ClockedLTL_NonMTL

.PHONY: all clean

all: $(EXAMPLE).vo $(ZEROINIT).vo $(FINAL).vo $(ABSTRACT).vo $(INSTANCE).vo $(NONMTL).vo

$(CORE).vo: $(CORE).v
	$(COQC) $<

$(PROOF).vo: $(PROOF).v $(CORE).vo
	$(COQC) $<

$(EXAMPLE).vo: $(EXAMPLE).v $(PROOF).vo
	$(COQC) $<

$(ZEROINIT).vo: $(ZEROINIT).v $(PROOF).vo
	$(COQC) $<

$(SOUND).vo: $(SOUND).v $(CORE).vo
	$(COQC) $<

$(PACK).vo: $(PACK).v $(CORE).vo
	$(COQC) $<

$(CONCRETE).vo: $(CONCRETE).v $(SOUND).vo $(PACK).vo
	$(COQC) $<

$(COMPLETE).vo: $(COMPLETE).v $(CONCRETE).vo
	$(COQC) $<

$(FINAL).vo: $(FINAL).v $(COMPLETE).vo $(PROOF).vo
	$(COQC) $<

clean:
	rm -f *.vo *.vos *.vok *.glob .*.aux


$(ABSTRACT).vo: $(ABSTRACT).v $(CORE).vo
	$(COQC) $<

$(INSTANCE).vo: $(INSTANCE).v $(ABSTRACT).vo $(PROOF).vo
	$(COQC) $<

$(NONMTL).vo: $(NONMTL).v $(ABSTRACT).vo
	$(COQC) $<
