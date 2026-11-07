import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 486 of the cap-17 certificate: slots 248832 .. 249343 -/
theorem chk_486 : chunkCheck 17 T stdSt 248832 512 = true := by decide +kernel

end Row17
