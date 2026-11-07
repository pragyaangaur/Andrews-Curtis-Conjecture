import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 265 of the cap-17 certificate: slots 135680 .. 136191 -/
theorem chk_265 : chunkCheck 17 T stdSt 135680 512 = true := by decide +kernel

end Row17
