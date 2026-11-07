import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 419 of the cap-17 certificate: slots 214528 .. 215039 -/
theorem chk_419 : chunkCheck 17 T stdSt 214528 512 = true := by decide +kernel

end Row17
