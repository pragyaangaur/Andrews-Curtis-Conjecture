import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 313 of the cap-17 certificate: slots 160256 .. 160767 -/
theorem chk_313 : chunkCheck 17 T stdSt 160256 512 = true := by decide +kernel

end Row17
