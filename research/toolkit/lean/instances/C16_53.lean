import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 53 of the cap-16 certificate: slots 54272 .. 55295 -/
theorem chk_53 : chunkCheck 16 T stdSt 54272 1024 = true := by decide +kernel

end Row16
