import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 2 of the cap-16 certificate: slots 2048 .. 3071 -/
theorem chk_2 : chunkCheck 16 T stdSt 2048 1024 = true := by decide +kernel

end Row16
