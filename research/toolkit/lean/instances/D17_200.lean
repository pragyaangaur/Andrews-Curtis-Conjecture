import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 200 of the cap-17 certificate: slots 102400 .. 102911 -/
theorem chk_200 : chunkCheck 17 T stdSt 102400 512 = true := by decide +kernel

end Row17
