FROM python:3.8-slim
WORKDIR /app
COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt
COPY Scripts /app/Scripts
COPY verify_file.py /app/
CMD ["python", "-m", "http.server", "8888"]
