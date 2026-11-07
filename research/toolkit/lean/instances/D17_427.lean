import RowBase

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row17

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 427 of the cap-17 certificate: slots 218624 .. 219135 -/
theorem chk_427 : chunkCheck 17 T stdSt 218624 512 = true := by decide +kernel

end Row17
