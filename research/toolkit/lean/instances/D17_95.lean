import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 95 of the cap-17 certificate: slots 48640 .. 49151 -/
theorem chk_95 : chunkCheck 17 T stdSt 48640 512 = true := by decide +kernel

end Row17
