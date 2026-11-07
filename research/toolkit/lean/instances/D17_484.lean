import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 484 of the cap-17 certificate: slots 247808 .. 248319 -/
theorem chk_484 : chunkCheck 17 T stdSt 247808 512 = true := by decide +kernel

end Row17
