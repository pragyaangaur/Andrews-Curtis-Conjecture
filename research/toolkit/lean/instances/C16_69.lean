import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 69 of the cap-16 certificate: slots 70656 .. 71679 -/
theorem chk_69 : chunkCheck 16 T stdSt 70656 1024 = true := by decide +kernel

end Row16
