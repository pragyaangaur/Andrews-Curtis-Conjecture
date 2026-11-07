import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 113 of the cap-16 certificate: slots 115712 .. 116735 -/
theorem chk_113 : chunkCheck 16 T stdSt 115712 1024 = true := by decide +kernel

end Row16
