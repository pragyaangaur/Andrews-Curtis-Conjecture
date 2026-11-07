import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 120 of the cap-17 certificate: slots 61440 .. 61951 -/
theorem chk_120 : chunkCheck 17 T stdSt 61440 512 = true := by decide +kernel

end Row17
