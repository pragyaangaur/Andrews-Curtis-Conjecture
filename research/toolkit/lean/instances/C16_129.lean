import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 129 of the cap-16 certificate: slots 132096 .. 133119 -/
theorem chk_129 : chunkCheck 16 T stdSt 132096 1024 = true := by decide +kernel

end Row16
