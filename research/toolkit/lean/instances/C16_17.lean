import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 17 of the cap-16 certificate: slots 17408 .. 18431 -/
theorem chk_17 : chunkCheck 16 T stdSt 17408 1024 = true := by decide +kernel

end Row16
