import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 464 of the cap-17 certificate: slots 237568 .. 238079 -/
theorem chk_464 : chunkCheck 17 T stdSt 237568 512 = true := by decide +kernel

end Row17
