import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 196 of the cap-16 certificate: slots 200704 .. 201727 -/
theorem chk_196 : chunkCheck 16 T stdSt 200704 1024 = true := by decide +kernel

end Row16
