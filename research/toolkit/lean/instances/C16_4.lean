import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 4 of the cap-16 certificate: slots 4096 .. 5119 -/
theorem chk_4 : chunkCheck 16 T stdSt 4096 1024 = true := by decide +kernel

end Row16
