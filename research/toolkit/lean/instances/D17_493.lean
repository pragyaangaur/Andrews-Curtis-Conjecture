import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 493 of the cap-17 certificate: slots 252416 .. 252927 -/
theorem chk_493 : chunkCheck 17 T stdSt 252416 512 = true := by decide +kernel

end Row17
