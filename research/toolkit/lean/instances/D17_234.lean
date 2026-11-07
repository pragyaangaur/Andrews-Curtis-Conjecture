import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 234 of the cap-17 certificate: slots 119808 .. 120319 -/
theorem chk_234 : chunkCheck 17 T stdSt 119808 512 = true := by decide +kernel

end Row17
