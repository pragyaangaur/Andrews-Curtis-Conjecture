import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 429 of the cap-17 certificate: slots 219648 .. 220159 -/
theorem chk_429 : chunkCheck 17 T stdSt 219648 512 = true := by decide +kernel

end Row17
