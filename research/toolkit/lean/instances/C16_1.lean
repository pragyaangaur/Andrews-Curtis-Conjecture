import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 1 of the cap-16 certificate: slots 1024 .. 2047 -/
theorem chk_1 : chunkCheck 16 T stdSt 1024 1024 = true := by decide +kernel

end Row16
