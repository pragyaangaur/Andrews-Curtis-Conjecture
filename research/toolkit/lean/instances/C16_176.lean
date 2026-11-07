import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 176 of the cap-16 certificate: slots 180224 .. 181247 -/
theorem chk_176 : chunkCheck 16 T stdSt 180224 1024 = true := by decide +kernel

end Row16
