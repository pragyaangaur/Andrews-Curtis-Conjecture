import RowBase_16

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace Row16

open ACBounds ACClosed ACKeys ACPack ACSlot

/-- chunk 155 of the cap-16 certificate: slots 158720 .. 159743 -/
theorem chk_155 : chunkCheck 16 T stdSt 158720 1024 = true := by decide +kernel

end Row16
