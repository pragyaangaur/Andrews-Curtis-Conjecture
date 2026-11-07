import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 52 of the cap-17 certificate: slots 26624 .. 27135 -/
theorem chk_52 : chunkCheck 17 T stdSt 26624 512 = true := by decide +kernel

end Row17
