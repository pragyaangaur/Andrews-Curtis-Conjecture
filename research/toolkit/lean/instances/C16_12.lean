import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 12 of the cap-16 certificate: slots 12288 .. 13311 -/
theorem chk_12 : chunkCheck 16 T stdSt 12288 1024 = true := by decide +kernel

end Row16
