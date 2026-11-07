import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 72 of the cap-16 certificate: slots 73728 .. 74751 -/
theorem chk_72 : chunkCheck 16 T stdSt 73728 1024 = true := by decide +kernel

end Row16
