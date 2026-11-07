import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 121 of the cap-16 certificate: slots 123904 .. 124927 -/
theorem chk_121 : chunkCheck 16 T stdSt 123904 1024 = true := by decide +kernel

end Row16
