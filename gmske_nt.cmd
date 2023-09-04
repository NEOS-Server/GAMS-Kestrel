@echo off
set fileDir=%~5
set gmsPython=%fileDir%GMSPython\python.exe

if exist "%gmsPython%" (
    set SSL_CERT_FILE=%fileDir%GMSPython\Lib\site-packages\certifi\cacert.pem
    "%gmsPython%" "%fileDir%gmske_nx.py" "%~4"
) else (
    python "%fileDir%gmske_nx.py" "%~4"
)
if not %ERRORLEVEL% == 0 echo ERR: Solver rc %ERRORLEVEL% 1>&2
