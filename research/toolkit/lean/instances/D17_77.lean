import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 77 of the cap-17 certificate: slots 39424 .. 39935 -/
theorem chk_77 : chunkCheck 17 T stdSt 39424 512 = true := by decide +kernel

end Row17
