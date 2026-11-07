import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 134 of the cap-16 certificate: slots 137216 .. 138239 -/
theorem chk_134 : chunkCheck 16 T stdSt 137216 1024 = true := by decide +kernel

end Row16
