import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 332 of the cap-17 certificate: slots 169984 .. 170495 -/
theorem chk_332 : chunkCheck 17 T stdSt 169984 512 = true := by decide +kernel

end Row17
