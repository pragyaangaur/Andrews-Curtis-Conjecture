import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 443 of the cap-17 certificate: slots 226816 .. 227327 -/
theorem chk_443 : chunkCheck 17 T stdSt 226816 512 = true := by decide +kernel

end Row17
